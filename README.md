# bcnode-rick
## It's really weird. It's about to get a whole lot weirder, Morty.
Build the new image using something like this:

```
docker build -t "blockcollider/bcnode:0.8.2-mpxc" .
```

Afterwards, run it as usual:

```
docker run --name bcnode -p 3000:3000 blockcollider/bcnode:0.8.2-mpxc start --ws --rovers --ui --node --miner-key <YOUR-KEY>
```
